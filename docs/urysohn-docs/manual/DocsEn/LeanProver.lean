import VersoManual
import Docs.Papers

open Verso.Genre Manual
open Verso.Code.External
open InlineLean
open Verso.Genre.Manual.Docs (citetOther citepOther citehereOther)
open Docs (refAvigad2024Theorem refAvigad2021Theorem refMathlib refBailey2024Type
  refSorensen2006Lectures refCoquand1986Calculus refPierce2002Types refCarneiro2019Type
  refCarneiro2024Lean4Lean refTacticas refMoogle refGao2024Semantic)

set_option pp.rawOnError true
-- Keep this in every translated chapter so bibliography text renders in English:
set_option docs.bib.lang "en"

set_option verso.exampleProject "../../.."

#doc (Manual) "Lean Theorem Prover" =>
%%%
tag := "lean-theorem-prover"
file := "lean-theorem-prover"
%%%

As mathematics becomes more technical and specialised, rigorously verifying formal proofs is an increasingly costly task. Motivated by the wish to make it easier, recent decades have seen a growing interest in the computational verification of theorems, leading to the development of systems such as Lean, Coq or Isabelle.

Within this field, we distinguish two kinds of formal verification systems: interactive ones (ITPs), which provide an environment where the user guides the proof process step by step, focusing on the "verification" aspect, and automatic ones (ATPs), which aim to complete proofs in a fully autonomous way{citepOther refAvigad2024Theorem}[] (Section 1).

In this work we will focus on the use of the *Lean Theorem Prover*, introduced in 2013 by Leonardo de Moura at Microsoft Research. It is a verifier whose goal is to reduce the distance between assisted and automated proofs, combining a language based on dependent type theory with tools that allow simple sub-problems to be delegated to the system.

Although here we will restrict ourselves to its use as a proof assistant, Lean is also a fully-fledged functional programming language, which offers the user broad possibilities for customisation and automation{citepOther refAvigad2024Theorem}[] (Section 1).

In this system, it is possible to define mathematical objects, state properties about them, and prove that those properties hold. This task is made easier by _Mathlib_, an extensive library of mathematics formalised in Lean, developed collaboratively by an active and constantly growing community{citepOther refMathlib}[].

Proofs are automatically verified by Lean's logical kernel, which guarantees their correctness through an expressive and rigorous type system. Lean's reliability as a proof assistant lies precisely in the simplicity and robustness of this kernel{citepOther refBailey2024Type}[].

In this section we will mainly follow the online manual _Theorem Proving in Lean 4_{citepOther refAvigad2024Theorem}[], which is an updated version of the book _Theorem Proving in Lean_{citepOther refAvigad2021Theorem}[], published in 2021, adapted to the new version of Lean. At the theoretical level there is no great difference between the two, so both references are valid for understanding the foundations we present here.

# Lean's type theory
%%%
file := "teoria-de-tipos"
%%%

Zermelo–Fraenkel set theory with the axiom of choice (ZFC) is the foundational basis chosen to formalise most of the mathematics we know. In this framework, all mathematical objects (numbers, functions, algebraic structures, etc.) can be represented as sets, built from a few basic axioms.

However, this system lacks a differentiated internal structure: every mathematical object, such as a number, a function, or even a collection of functions is, ultimately, a set. To achieve a clearer and more differentiated representation of mathematical objects, Lean uses, instead, a system based on types. Moreover, this approach offers us the possibility of establishing a correspondence between programs and mathematical proofs, known as the Curry–Howard correspondence{margin}[The Curry–Howard correspondence establishes a relationship between logic and programming; it lets us understand how "proving a proposition" and "constructing a term of a certain type" can be equivalent. We will see what this means in practice later on, but the deeper ideas, which are beyond the scope of this work, are presented in detail in {citehereOther refSorensen2006Lectures}[].].

In particular, Lean is founded on the _Calculus of Inductive Constructions_, an extension of the calculus of dependent types that incorporates inductive types and a countable non-cumulative hierarchy of universes{citep refCoquand1986Calculus}[]. Although it is not necessary to understand this system in order to use Lean as a proof assistant, below we give a brief explanation of the fundamental concepts: type theory, the lambda calculus, the addition of types to the latter, and the introduction of dependent types.

In this section we will see several fragments of Lean code. Lean has an interactive compiler that processes each line when the cursor is placed on it, displaying the result on screen. From now on, when a code fragment produces an output (for example, via `#check` or `#eval`), it will be shown in a separate block right below the code, with the same text that Lean would return.

## Type theory

Let us start with the most basic part: type theory. We change the paradigm from "every object is a set", typical of ZFC, to "every object is a term with an associated type". This allows us to structure mathematical objects and their relationships more clearly.

For example, $`3` is a term of type "natural" (`Nat`), while "true" is a term of type "boolean". In Lean, we can check the type of these expressions using the `#check` command.

```lean (name := checkBasic1)
#check 3
```
```leanOutput checkBasic1
3 : Nat
```
```lean (name := checkBasic2)
#check true
```
```leanOutput checkBasic2
Bool.true : Bool
```

As in this example, in Lean we use the symbol $`:` to describe typing information. That is, if $`x` is a term of type $`X`, we write $`x : X`.

On the other hand, a type, such as `Nat`, is also a term. We can check its type:

```lean (name := checkNatType)
#check Nat
```
```leanOutput checkNatType
Nat : Type
```

In Lean, types have their own type, which is called `Type`. This allows us to define new types. We can use the `variable` command to define objects in our code{margin}[We will look at this command in detail later.].

```lean -show
section VarX
```
```lean (name := varX1)
variable (X : Type)
#check X
```
```leanOutput varX1
X : Type
```
```lean (name := varX2)
variable (x : X)
#check x
```
```leanOutput varX2
x : X
```
```lean -show
end VarX
```

Now, we can combine different types to obtain more complex types. Let $`X` and $`Y` be two types. We can consider the type $`X \times Y`, which denotes the pairs formed by an element of $`X` and an element of $`Y`. The type we will use the most is $`X \to Y`, which denotes the functions from $`X` to $`Y`. Let us write this in Lean.

```lean -show
section VarXY
```
```lean (name := varXY1)
variable (X Y : Type)
#check X × Y
```
```leanOutput varXY1
X × Y : Type
```
```lean (name := varXY2)
variable (x : X) (y : Y)
#check (x, y)
```
```leanOutput varXY2
(x, y) : X × Y
```
```lean (name := varXY3)
#check X → Y
```
```leanOutput varXY3
X → Y : Type
```
```lean (name := varXY4)
variable (f : X → Y)
#check f
```
```leanOutput varXY4
f : X → Y
```

On the other hand, by juxtaposing simple terms, we can form more complex terms. In Lean, the typing rules dictate the type of these newly obtained terms. For example, if $`x` has type $`X` and $`f` has type $`A \to B`, as in the previous example, then $`f x` has type $`B`. Indeed:

```lean (name := applyFx)
#check f x
```
```leanOutput applyFx
f x : Y
```
```lean -show
end VarXY
```

As in the previous example, Lean can automatically deduce the type of many terms from the context. This capability is known as *type inference* and it often makes our work easier, allowing for more concise code.

# The lambda calculus
%%%
file := "calculo-lambda"
%%%

The Lambda Calculus, introduced by Alonzo Church in the 1930s, is a formal system that allows expressions to be built through two basic operations: abstraction and application{citepOther refPierce2002Types}[]. In this system, some expressions represent functions (using lambda notation) and others represent values to which those functions can be applied. Two expressions can be juxtaposed to form a new expression; if the first one is an abstraction, then it is interpreted as function application. From there, reductions can be performed to simplify the resulting expression when appropriate.

For example, a valid term could be $`\lambda n, n + 2`, which represents a function that can be applied to a value to obtain another one.

In Lean, we define functions using the `fun` command, which corresponds to the $`\lambda` notation of the classical lambda calculus{margin}[In the previous version of Lean, the notation `λ n, n + 2` was used; however, in this latest version it has been changed to `fun n ↦ n + 2` to improve code readability.]. For example{margin}[We will study the `def` command in detail later.]:

```lean -show
namespace LambdaEx1
```
```lean (name := lambdaFDef)
def f := fun n ↦ n + 2
```

Moreover, Lean supports reduction by function application on these terms. For example, if we apply the previous function to $`3`, $`(n \mapsto n + 2)3`, it can be reduced to $`3 + 2` by function application, and, assuming the operation $`+` was defined previously, we can reduce this expression to $`5`. We can check the result of this reduction using the `#eval` command.

```lean (name := lambdaFEval)
#eval f 3
```
```leanOutput lambdaFEval
5
```
```lean -show
end LambdaEx1
```

We will say that two terms that can be reduced in this way to the same value are *definitionally equal*. Lean treats terms that are definitionally equal as literally equal, as we will see in practice.

## Typed lambda calculus

The classical lambda calculus does not incorporate types: any function can be applied to any argument. To avoid inconsistencies and provide more structure, the typed lambda calculus is introduced, where each term is assigned a concrete type.

We can write the previous example in Lean as follows:

```lean -show
namespace LambdaEx2
```
```lean (name := typedLambdaF)
def f : Nat → Nat := fun n => 2 * n
```
```lean -show
end LambdaEx2
```

Here, we are indicating that $`f` has type $`\mathbb{N} \to \mathbb{N}`, that is, that it is a function that takes values in $`\mathbb{N}` and returns values in $`\mathbb{N}`. This information allows Lean to verify that expressions are well formed.

## Dependent type theory

In order to express the various mathematical objects in this theory, we need to introduce dependent types. A dependent type is one that can vary depending on a term.

For example, in Lean, the type `List α` represents a list of elements of type $`\alpha`. If we define an object of type `List α`, the type of this object will depend on the type $`\alpha` we assign to it. Internally, it is defined as a function of type `Type u → Type u`.

```lean (name := listDep1)
#check List
```
```leanOutput listDep1
List.{u} (α : Type u) : Type u
```
```lean (name := listDep2)
#check List Nat
```
```leanOutput listDep2
List Nat : Type
```

We can think of dependent types as a generalisation of functions from one type to another type, where the target type may depend on the input type. We call such functions "dependent functions".

In particular, the proposition $`\forall x \in \mathbb{N}, P x` is represented in Lean by a dependent type that expresses the set of functions that, given an element $`x \in \mathbb{N}`, return a proof of $`P x`. Lean's notation for this kind of construction is `Π x : ℕ, P x`. The $`\Pi` operator denotes that the output type may depend on the input value.

## Universe hierarchy

Since in type theory every element has a type, the type `Type` also has an associated type. But if we simply wrote `Type : Type`, the system would fall into an inconsistency similar to Russell's paradox. To avoid this, Lean introduces an infinite hierarchy of universes: `Type 0 : Type 1`, `Type 1 : Type 2`, and so on.

This hierarchy is non-cumulative, which means that if `A : Type u`, it is not assumed in general that `A : Type (u+1)`. This allows Lean to better control how types are combined and to avoid ambiguities when determining which universe each term belongs to, although it can perform certain conversions automatically when it is safe to do so. For this reason, in most cases it is not necessary to work explicitly with these universes.

## Inductive types

In Lean, the vast majority of types are instances of a family of types known as *inductive types*. An inductive type is a structure formed by a finite list of constructors, each with its corresponding type. Each constructor describes a valid way of building a term of this new type.

In Lean, we define an inductive type using the `inductive` keyword{margin}[Although in Lean inductive types are introduced as a primitive construction of the language, they can be defined equivalently purely in terms of dependent types. This reduction is formally explored in {citehereOther refCarneiro2019Type}[].].

```
inductive Foo where
  | constructor₁ : ... → Foo
  | constructor₂ : ... → Foo
  ...
  | constructorₙ : ... → Foo
```

A classic example of an inductive definition is the set of natural numbers, $`\mathbb{N}`. In Lean, we can describe the type `Nat` of natural numbers as

```lean -show
namespace Scratch
```
```lean (name := inductiveNatDemo)
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
```
```lean -show
end Scratch
```

Internally, the `inductive` declaration automatically generates a collection of axioms that define the type:

* A constant, `Nat`, which represents the new type.
* A series of introduction rules or constructors, which indicate the possible ways of building terms of the new type.
* An elimination rule, `Nat.rec`, which indicates the way of "using" a term of this type{margin}[The `#print` command shows the complete definition of the object, unlike `#check`, which only shows its type.].

```lean (name := printNatRec)
#print Nat.rec
```
```leanOutput printNatRec
recursor Nat.rec.{u} : {motive : Nat → Sort u} →
  motive Nat.zero → ((n : Nat) → motive n → motive n.succ) → (t : Nat) → motive t
number of parameters: 0
number of indices: 0
number of motives: 1
number of minors: 2
rules:
for Nat.zero (0 fields): fun motive zero succ => zero
for Nat.succ (1 fields): fun motive zero succ n => succ n (Nat.rec zero succ n)
```

That is, `inductive` can be seen as _syntactic sugar_ that automatically generates the following Lean code{margin}[We will study the `axiom` command in detail later.]:

```
axiom (Nat : Type)
axiom (zero : Nat)
axiom (succ : Nat → Nat)
axiom (Nat.rec : {motive : Nat → Sort u} → motive Nat.zero →
  ((n : Nat) → motive n → motive Nat.succ n) → (t : Nat) →
  motive t)
```

This last object, `Nat.rec`, encodes the principle of induction on the naturals{margin}[`Nat.rec` is a type that depends on `motive`, which is any property about the naturals. `Nat.rec` tells us that if `motive` holds for `Nat.zero` (`motive Nat.zero`), then if for each `n` (`n : Nat`) satisfying `motive` (`motive n`) we have that `n+1` satisfies `motive` (`motive Nat.succ n`), then `motive` holds for every `n` (`(t : Nat) → motive t`).]. This principle is used implicitly in many definitions by cases, for example:

```lean (name := addDef)
def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)
```

In this definition, we use the expression `match n with` to distinguish the two possible cases of a natural number: `zero` and `succ n`. Internally, Lean compiles this expression as an application of `Nat.rec`. We will see later how this principle of induction can be used not only to define functions, but also to prove properties about all the terms of an inductive type.

It is worth noting that there are other constructions in Lean, such as `structure` or `class`, which are internally defined as particular cases of inductive types, but are added as separate constructions to improve readability and functionality. We will see some examples of their use throughout this work.

Finally, through inductive types it is possible to define the logical connectives (negation, conjunction, disjunction and implication). This constitutes another big difference between set theory and the calculus of inductive constructions. In order to use set theory, it is necessary to have previously developed (first-order) logic. In this way, formal proofs are not mathematical objects, but live exclusively at the meta-theoretical level.

In the calculus of inductive constructions, on the other hand, logic is expressed within the theory itself, and proofs are mathematical objects that live inside it.

## Proofs as mathematical objects

Propositions, like any other object in this theory, are terms with an associated type. In Lean, this type is called `Prop`.

```lean (name := propCheck1)
#check Prop
```
```leanOutput propCheck1
Prop : Type
```
```lean (name := propCheck2)
#print True
```
```leanOutput propCheck2
inductive True : Prop
number of parameters: 0
constructors:
True.intro : True
```

```lean -show
section PropVarP
```
```lean (name := propVarP1)
variable (P : Prop)
#check P
```
```leanOutput propVarP1
P : Prop
```
```lean (name := propVarP2)
#check ¬ P
```
```leanOutput propVarP2
¬P : Prop
```
```lean -show
end PropVarP
```

In Lean, we interpret objects of type `Prop` as types in themselves and the proofs of each proposition as terms inhabiting that type, following the Curry–Howard correspondence. That is, a proposition `p : Prop` is the type of the proofs of `p`; an expression of the form `h : p` means that `h` is a proof of `p`. We say that a proposition `p` is true if we can construct a term of type `p`.

```lean -show
section PropVarPH
```
```lean (name := propVarPH)
variable (p : Prop)
variable (h : p)
#check h
```
```leanOutput propVarPH
h : p
```
```lean -show
end PropVarPH
```

This, together with dependent type theory, gives us a way of defining any mathematical result. For example, "being even" is a property that depends on a natural number $`n`, so we could describe it by `es_par : ℕ → Prop`. For each natural `n`, we obtain a term of type `Prop`.

```
def es_par : ℕ → Prop := ...
#check es_par    -- es_par : ℕ → Prop
#check es_par 3    -- es_par 3 : Prop
```

In this case, a term of type `es_par n` will be a proof that `n` is even.

Moreover, if `p : Prop` is a proposition, Lean recognises any two elements of type `p` (`h1 h2 : p`) as definitionally equal: it does not matter which concrete proof we have, only its existence matters. This is known as _proof irrelevance_.

This property has important consequences. On the one hand, it avoids undesired behaviour when we define structures that depend on propositions. For example, if we wanted to define a point of the first quadrant in $`\mathbb{R}^2` as a pair of the form `x y : ℝ × ℝ` together with a proof `h : x ≥ 0 ∧ y ≥ 0`, then, thanks to proof irrelevance, we can identify two points that have the same coordinates, because the proofs `h` and `h'` associated with each of them are the same.

On the other hand, this same property prevents access to the content of a proof. In particular, it is not possible to directly extract the witness from the proof of an existential proposition of the form $`\exists x, P(x)`, since all the proofs of that proposition are considered equal. Given a proof of $`\exists x, P(x)`, we have several methods for obtaining a witness, one of which is using the axiom of choice. We will come back to this question later.

One last remarkable feature of propositions in Lean is that logical implication is represented directly by functions: given two propositions `p q : Prop`, a proof of `p → q` is simply a function that, given a proof of `p`, returns a proof of `q`. This identification between functions and implications is another manifestation of the Curry–Howard correspondence.

In summary, in order to express a mathematical result in this language, we have to write a term of the form `p : Prop`. To prove that the result is true, we must construct a term `h : p`. Lean's job as a proof assistant is to verify that the term `h` is well constructed and has the correct type.

# Why should we trust Lean?
%%%
file := "por-que-fiarnos-de-lean"
%%%

Now that we have described the way in which a result is considered proved in Lean, it makes sense to ask the question: why should we trust Lean's type inference? What guarantees do we have that the proofs Lean accepts are really correct?

As we have pointed out, proving a result in Lean consists of correctly constructing a term that has a certain type. This process is analogous to verifying programs: it is a matter of checking that a term is well formed (following concrete rules) and satisfies a given specification, expressed as a type. This task falls to Lean's kernel, a small program that contains the minimal implementation of Lean's internal logic.

The remaining components of Lean that we interact with to build proofs (such as the tactics we will see later) return constructions expressed in the language of the Lean kernel{citepOther refBailey2024Type}[]. This means that trusting Lean really comes down to trusting its kernel{margin}[This idea is known as the _de Bruijn criterion_, which proposes that a formal verifier should produce its proofs in the language of a small kernel, even if other, more complicated methods are used to construct those proofs in the first place ({citehereOther refBailey2024Type}[]).].

Now, why do we trust Lean's kernel? Thanks to the kernel being small and isolated from the rest of the system, it is possible to write independent implementations of it that autonomously verify the proofs accepted by Lean. Lean allows these proofs to be exported in an intermediate format that contains all the information needed to reconstruct and validate them externally. Moreover, since this format is modular, it is possible to validate only certain specific aspects of the kernel{citepOther refBailey2024Type}[]. For example, Carneiro{citepOther refCarneiro2024Lean4Lean}[] describes a new external implementation of the Lean 4 type checker, written in the Lean language itself and capable of verifying the whole Mathlib library.

# Proofs in Lean
%%%
file := "demostraciones-en-lean"
%%%

So far, we have explored the dependent type theory on which Lean is built, as well as the foundations that guarantee the correctness of its proofs. We therefore move on to a more practical approach: how do we write mathematics in Lean?

Let us remember that formalising a result in Lean does not consist only of writing its statement, but also of constructing a proof step by step, with no omissions and with total precision. Here, it is never enough to write "trivial" when we believe we should already know something: we need to convince the system that every step is valid.

This section is devoted to learning how to write proofs in Lean. We will see how to introduce new objects into our context, how to state propositions and how to build proofs by interacting with Lean. We will also present some automation tools and methods for relying on the Mathlib library.

## Axioms, definitions and variables

Before writing proofs in any formal system, we need to describe the *context* in which we work: the set of objects and hypotheses available at a given moment. This context is dynamic and expands as we introduce new elements.

The same happens in Lean. The system maintains and constantly updates this context to check that each expression is well formed and has the expected type.

We can introduce new information into the context in different ways. We distinguish between axioms, definitions and variables, each with a different logical function in the system.

* *Axioms*{margin}[In Lean 3, this kind of declaration was called a _constant_ and used the `constant` command.]

They allow us to introduce hypotheses that are assumed without proof. In particular, writing that x "has type X" is also a hypothesis, so axioms can be used to introduce new objects{margin}[In this sense we said that defining an inductive type is analogous to writing a collection of axioms. `inductive Nat` can be seen as a structured version of `axiom Nat : Type`, `axiom zero : Nat`, `axiom succ : Nat to Nat`, etc.]. For example:

```lean -show
namespace AxiomP
```
```lean (name := axiomPH)
axiom P : Prop
axiom h : P → P
```
```lean -show
end AxiomP
```

We are declaring a proposition $`P` and a proof that $`P` implies $`P`.

```lean -show
namespace AxiomN
```
```lean (name := axiomNHn)
axiom n : Nat
axiom hn : n > 2
```
```lean -show
end AxiomN
```

Here we are assuming that $`n` is a natural number greater than $`2`.

Thus, axioms allow us to fix facts that we want to assume as valid throughout our proofs.

* *Definitions*

They introduce new objects from already known ones. Unlike axioms, it is not enough to indicate the type of the new object; its construction must also be given. For example:

```lean -show
namespace DefsBlock
```
```lean (name := defsFNEspar)
def f : Nat → Nat := fun n ↦ 2 * n
def n : Nat := 3
def es_par : Nat → Prop := fun n ↦ ∃ m, n = f m
```
```lean -show
end DefsBlock
```

Moreover, when the type can be inferred from the construction, it is not necessary to indicate it explicitly:

```lean (name := defNInfer)
def n := 3
#check n
```
```leanOutput defNInfer
n : Nat
```

* *Variables*

In most programming languages, we are used to defining a variable implying assigning a concrete value to it. However, in Lean variables behave more like they do in logic. When introducing a variable $`x`, what is introduced is a universal context: whenever $`x` appears free, Lean will interpret that what follows is universally quantified with respect to $`x`. For example{margin}[Variables, unlike axioms and definitions, are written between parentheses. The same happens with the arguments taken by propositions, as we will see later. This is related to the Curry–Howard correspondence: declaring a variable amounts to abstracting over it, which corresponds to quantifying universally.]:

```lean -show
section VarXAxiomHx
```
```lean (name := varXAxiomHx)
variable (x : Nat)
axiom hx : x ≥ 0
#print hx
```
```leanOutput varXAxiomHx
axiom hx : ∀ (x : Nat), x ≥ 0
```
```lean -show
end VarXAxiomHx
```

## Propositions

Besides introducing objects, we also want to state and prove propositions. In Lean, this is done in the same way as in other formal systems: we first write the results (as lemmas or theorems) formally, and then we provide a proof.

As we have already seen, a proposition in Lean is a term of type `Prop`, and a proof of `p : Prop` is simply a term of type `p`. Therefore, proving a proposition is no different from defining an object; we can use `def` to write mathematical results. For example:

```
def mi_prop : 1 > 0 := ...
```

Here we are saying that `mi_prop` is an object of type `1 > 0`. If in the place of `...` we provide a term of type `1 > 0`, we will have proved `mi_prop`.

However, for greater clarity and structure, Lean provides the `lemma` and `theorem` commands. Both work exactly like `def` and are interchangeable with each other, but they make the code easier to read by indicating which objects are mathematical results, and the hierarchy of importance among them. The syntax is the same:

```
lemma my_lemma : 1 > 0 := ...
theorem commutative_sum (a b : ℕ) : a + b = b + a := ...
```

There is also the `example` command, which is used to write proofs without the need to name the result:

```
example (a b : ℕ) : a * b = b * a := ...
```

This kind of expression does not extend the context or define new objects; they are simply local checks. But we will see that they can be useful to us on certain occasions.

## Proofs: tactic mode

We arrive at the central part of this section: *writing proofs* in Lean. In general, there are two ways of constructing a proof in Lean:

* By means of *terms*, that is, directly writing an expression of the desired type.
* By means of *tactic mode*, in which a proof is built step by step using instructions called *tactics*.

In this work we will use tactic mode exclusively, since it is the most practical approach and the closest to the way we reason when writing mathematical proofs in natural language.

In an informal proof, we usually advance through chained logical steps: "suppose that...", "then...", "by the lemma..., we have...". Each of these steps is translated in Lean through a tactic: an instruction that modifies the state of the proof, whether by introducing hypotheses, applying known results, splitting the goal into more manageable parts, etc.

Moreover, tactic mode allows us to work *interactively* with Lean. If we write a statement, and immediately after `:=` we write `by`, we are telling Lean that we are going to use tactic mode for the construction of this term. For example:

```anchor by_pq_and (module := UrysohnsLemma.Docs.Tactics)
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
```

We are indicating that we want to construct a term of type `p ∧ q` from the hypotheses `hp : p` and `hq : q`, and that we are going to use tactic mode for that construction.

Internally, Lean interprets this by generating a local context (our hypotheses) and a *goal* (our thesis), which consists of constructing the term of the expected type. After `by`, we can start writing tactics, which Lean will interpret by updating the context and the goals.

This goal is reflected in the *InfoView*, a window that shows the current state of our proof. Lean processes line by line automatically, so at any moment we can consult the impact of having applied a tactic simply by placing the cursor on the corresponding line of code.

In fact, the InfoView also shows the results of the instructions we have already seen, such as `#check`, `#print` or `#eval`.

![Screenshot of Lean's InfoView showing the result of checking the type of an expression with the #check command.](figuras/check-example-light-version.png)

In general, while writing in Lean, we will have this window open alongside our code, so that we can watch the progress of our proof.

![Screenshot of Lean's InfoView showing the tactic state of a proof, with the hypothesis context and the goal marked with the symbol ⊢.](figuras/theorem-example-light-version.png)

Under the `Tactic state` section, we can check:

* The number of goals we still have to prove (in this case just one: `1 goal`).
* Our context.
* The goal (or goals), marked with the symbol `⊢`.

From this point on, we can start adding the tactics that will make up our proof. Tactics are written one after another, separated by semicolons (`;`) or by line breaks.

When writing a tactic, the `Tactic state` section of the InfoView will update accordingly. When all the goals have been solved, the InfoView will show `No goals`.

![Screenshot of Lean's InfoView showing the No goals message once the proof has been completed.](figuras/no-goals-example-light-version.png)

## Some basic tactics

In this section we will see some of the most basic and useful tactics for constructing proofs in Lean. We will see how they are applied and what effect they have on the InfoView. The rest of the tactics that appear throughout this work can be consulted in the tactics section of the Lean documentation{citepOther refTacticas}[].

In order to use the tactics mentioned below, it is necessary to import the Mathlib module corresponding to tactic mode via

```anchor import_mathlib_tactic (module := UrysohnsLemma.Docs.Tactics)
import Mathlib.Tactic
```

From here on, instead of showing screenshots of the InfoView, we will use two code blocks side by side: the one on the left contains the Lean code; the one on the right represents the state that would be shown in the InfoView if we placed the cursor on the last line.

### `intro`

The `intro` tactic introduces a new object into the context, similar to writing "Suppose that..." or "Let..." in an informal proof.

It is useful when the goal has the form of an implication or a universal quantifier: we turn the first part of the goal into a new hypothesis and the second part into the new goal. For example, for the implication:

```anchor intro_before1 (module := UrysohnsLemma.Docs.Tactics)
example (p : Prop) : p → p := by
```

↓

```anchor intro_after1 (module := UrysohnsLemma.Docs.Tactics)
example (p : Prop) : p → p := by
  intro hp
```

And for removing quantifiers:

```anchor intro_before2 (module := UrysohnsLemma.Docs.Tactics)
example : ∀ (p : Prop), p → p := by
```

↓

```anchor intro_after2 (module := UrysohnsLemma.Docs.Tactics)
example : ∀ (p : Prop), p → p := by
  intro q
```

### `exact`

The `exact` tactic is used when we already have, in our context, exactly what we want to prove. That is, there is a hypothesis that matches the current goal. For example:

```anchor exact_before1 (module := UrysohnsLemma.Docs.Tactics)
example : ∀ (p : Prop), p → p := by
  intro p hp
```

↓

```anchor exact_after1 (module := UrysohnsLemma.Docs.Tactics)
example : ∀ (p : Prop), p → p := by
  intro p hp
  exact hp
```

By way of comparison, we could construct this proof using only terms in the following way:

```anchor exact_term_mode (module := UrysohnsLemma.Docs.Tactics)
example : ∀ (p : Prop), p → p := fun p ↦ (fun hp : p ↦ hp)
```

In this case it may turn out simpler, but in more complex proofs we lose readability.

### `apply`

The `apply` tactic allows us to use an implication to reduce a goal to a simpler one. It amounts to using the _Modus Ponens_ rule: if we have a hypothesis of the form $`p \rightarrow q` and we want to prove $`q`, it suffices to prove $`p`.

```anchor apply_before (module := UrysohnsLemma.Docs.Tactics)
example (p q : Prop) (hp : p)
    (hpq : p → q) : q := by
```

↓

```anchor apply_after (module := UrysohnsLemma.Docs.Tactics)
example (p q : Prop) (hp : p)
    (hpq : p → q) : q := by
  apply hpq
```

We could complete this proof using `exact hp`.

### `use`

We use `use` to work with the existential quantifier. If we want to prove a proposition of the form "$`\exists x, P x`", it suffices to find a concrete $`x_0` that satisfies the property $`P`.

In this case, we apply `use` to tell Lean the concrete value $`x_0` that we want to use to prove existence. The goal then becomes proving that $`x_0` satisfies $`P`. For example:

```anchor use_before (module := UrysohnsLemma.Docs.Tactics)
example : ∃ n : ℕ, n > 3 := by
```

↓

```anchor use_after (module := UrysohnsLemma.Docs.Tactics)
example : ∃ n : ℕ, n > 3 := by
  use 5
```

### `left`, `right`

The `left` and `right` tactics are used to work with disjunctions, that is, propositions of the form $`A \lor B`.

In an informal proof, if we want to show that "$`A` or $`B`" is true, it is enough to prove one of the two. We use `left` to indicate that we are going to prove the left part ($`A`), and `right` if we want to prove the right part ($`B`). For example:

```anchor leftright_before (module := UrysohnsLemma.Docs.Tactics)
example (p q : Prop) (hp : p) :
    p ∨ q := by
```

↓

```anchor leftright_after (module := UrysohnsLemma.Docs.Tactics)
example (p q : Prop) (hp : p) :
    p ∨ q := by
  left
```

We could complete this proof by applying `exact hp`.

### `constructor`

We use `constructor` to work with conjunctions, that is, propositions of the form $`A \land B`.

When we want to prove that "$`A` and $`B`" is true, we can prove $`A` on one side and $`B` on the other. When applying `constructor`, Lean splits a goal `A ∧ B` into two sub-goals with the same context: one for `A` and another for `B`. For example:

```anchor constructor_before (module := UrysohnsLemma.Docs.Tactics)
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
```

↓

```anchor constructor_after (module := UrysohnsLemma.Docs.Tactics)
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
  constructor
```

After applying `constructor`, the InfoView will show two pending goals (`2 goals`). By solving each one separately, we complete the proof.

```anchor constructor_complete (module := UrysohnsLemma.Docs.Tactics)
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
  constructor
  exact hp
  exact hq
```

Although the above is correct, the usual practice when working with more than one goal is to use `·` to separate them. When we write `·` after a line break, Lean focuses on the first goal, temporarily hiding the rest. For example:

```anchor constructor_dot_before (module := UrysohnsLemma.Docs.Tactics)
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
  constructor
  ·
```

If we place the cursor at the end, the InfoView only shows `1 goal`, because the second goal is hidden for now. The complete proof in this style would be:

```anchor constructor_dot_complete (module := UrysohnsLemma.Docs.Tactics)
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq
```

### `cases'`

The `cases'` tactic is used to analyse a disjunction in the context, that is, a hypothesis of the form $`A \lor B`.

In an informal proof, it amounts to reasoning by cases: "Suppose $`A` holds, and let us see whether the goal follows; suppose then that $`B` holds, and let us check whether it also follows".

When applying `cases' h` to a hypothesis h, Lean duplicates the goal (which does not change), but modifies the context in each of the new goals, introducing the hypotheses corresponding to each case. We use the `with` keyword to assign names to the new hypotheses. For example:

```anchor cases_before (module := UrysohnsLemma.Docs.Tactics)
example (p q : Prop) (h : p ∨ q)
    (hpq : p → q) : q := by
```

↓

```anchor cases_after (module := UrysohnsLemma.Docs.Tactics)
example (p q : Prop) (h : p ∨ q)
    (hpq : p → q) : q := by
  cases' h with hp hq
```

We can then complete the proof with the tools we have so far:

```anchor cases_complete (module := UrysohnsLemma.Docs.Tactics)
example (p q : Prop) (h : p ∨ q)
    (hpq : p → q) : q := by
  cases' h with hp hq
  · apply hpq
    exact hp
  · exact hq
```

As we have seen through these examples, completing a proof in tactic mode consists of combining these instructions one after another, making the hypotheses and the goals advance until reaching the desired state: `No goals`. Tactics give us the flexibility needed to formalise a wide variety of mathematical results.

## Automation tools and searching Mathlib

As proofs in Lean become more complex, it is not always practical to build every step manually. To speed up the process, Lean incorporates some automation tools that allow certain tasks to be delegated to the system.

Moreover, instead of proving again results that are already formalised, it is essential to *take advantage of Lean's mathematical library, Mathlib*, which contains thousands of definitions and theorems available for reuse.

However, relying on Mathlib is not always straightforward: results may have unintuitive or very specific names, and finding the lemma we need at a given moment is not always easy.

For example, a result as simple as: "If $`a, b, c` are real numbers such that $`a < b` and $`c < 0`, then $`a + c < b`" (which in an informal proof we would consider almost trivial), appears in Mathlib under the name `add_lt_of_lt_of_neg'`. In practice, remembering all these names is unfeasible, even for elementary results.

In this section we will introduce the `simp` and `exact?` tactics, which help us solve simple goals, and two external tools we can use to locate results in Mathlib. We will also see how to integrate these tools into our result-proving process.

### `simp`

The simplest way to rely on the Mathlib library is to use the `simp` tactic. This tactic performs an exhaustive search through a database of Mathlib lemmas that are marked with the `simp` attribute, trying to simplify as much as possible the goal or the hypotheses it is applied to.

The `simp` tactic can be used at any moment of the proof, but it is especially useful when something we want to prove seems evident or simple enough. For example:

```anchor simp_group (module := UrysohnsLemma.Docs.Automation)
example (G : Type) [Group G] (a b c : G) :
    a * a⁻¹ * 1 * b = b * c * c⁻¹ := by
  simp
```

Just by using `simp` we can finish the proof in this case. Really, all it does is repeatedly rewrite results of the form `A = B` or `A ↔ B`, until it cannot rewrite anything else, in a mechanical way. Therefore, although it is useful in many cases, in others it may not help us.

In practice, when it is easy for us to use other tactics or known results, that will be preferable to using `simp`: first because, being an exhaustive search, it is not a computationally efficient tactic, and second because it worsens the readability of the code, since it is sometimes hard to know how certain simplifications happen.

### `exact?`

Lean incorporates some tactics that try to close the current goal using both the hypotheses of the context and the results available in the imported files. The most notable ones are `exact?`{margin}[The `exact?` tactic was called `library_search` in Lean 3.] and `apply?`.

Throughout the project, the one I have used most frequently is `exact?`. This tactic tries to find an expression that has exactly the type of the current goal, searching both in the local information (context hypotheses, previously defined results) and in the Mathlib library.

For example, in the case of finding local hypotheses:

```anchor exactq_local (module := UrysohnsLemma.Docs.Automation)
example (p : Prop) : p → p := by
  intro hp
  exact?
```

And in the case of finding Mathlib results:

```anchor exactq_mathlib (module := UrysohnsLemma.Docs.Automation)
example (n : ℕ) : n ≥ 0 := by
  exact?
```

In general, using the expression suggested by `exact?` will conclude the proof.

Even though `exact?` can help us in many cases, it is a relatively simple tool, which can only take one step (applying a theorem or a hypothesis). This implies that if we do not have the exact hypotheses of the theorems as they appear in Mathlib, `exact?` will not find any solution.

When working with more complex hypotheses, the usual approach is not to use `exact?` directly to prove our goal, but to prove certain intermediate results. For this reason, a crucial tactic when working with `exact?` is `have`, the equivalent in informal proofs of stating a lemma in the middle of a proof. For example, suppose we want to prove:

```anchor have_goal_r_stmt (module := UrysohnsLemma.Docs.Automation)
example (p q r : Prop) (hpq : p → q) (hqr : q → r) (hp : p) : r
```

Instead of trying to prove `r` immediately, we could prove, as an intermediate step, that `q` holds. For this we use `have`:

```anchor have_goal_r_incomplete (module := UrysohnsLemma.Docs.Automation)
example (p q r : Prop) (hpq : p → q)
    (hqr : q → r) (hp : p) : r := by
  have hq : q
```

Writing `have hq : q` introduces a new goal, `q`, independent from the previous one. Once we complete the proof of this new goal, we will be able to use the result in our proof. Therefore, we could complete the previous example in the following way:

```anchor have_goal_r_complete (module := UrysohnsLemma.Docs.Automation)
example (p q r : Prop) (hpq : p → q) (hqr : q → r) (hp : p) : r := by
  have hq : q
  · apply hpq
    exact hp
  apply hqr
  exact hq
```

Remember that we use the dot `·` to separate the proof of `hq` from the rest of the proof.

Let us see, then, what the process of working with `exact?` looks like. Consider the following example, for which `exact?` does not find any result:

```
example (x : ℝ) (hx : x > 0) :
    x / x = 1 := by
  exact?
```

_State in the InfoView:_

```
Tactic state
  1 goal
  x : ℝ
  hx : x > 0
  ⊢ x / x = 1
Messages
  `exact?` could not close the goal.
```

1. Looking at the current state of the proof, identify what hypothesis we would like to have in our context. In this case, since a division is involved, it might be necessary to have the hypothesis $`x \neq 0`.
1. Add the new goal using `have`{margin}[In some cases, it will be more useful to write what we believe we may need outside the proof, using `example`, because we will be able to write more general results.].

  ```anchor xdivx_have_empty (module := UrysohnsLemma.Docs.Automation)
  example (x : ℝ) (hx : x > 0) :
      x / x = 1 := by
    have h : x ≠ 0
    ·
  ```
1. Try to prove the new goal using `exact?`.

  ```anchor xdivx_have_exactq (module := UrysohnsLemma.Docs.Automation)
  example (x : ℝ) (hx : x > 0) :
      x / x = 1 := by
    have h : x ≠ 0
    · exact?
  ```

With this new hypothesis, it seems likely that `exact?` will be able to finish the proof. Indeed:

```anchor xdivx_complete (module := UrysohnsLemma.Docs.Automation)
example (x : ℝ) (hx : x > 0) :
    x / x = 1 := by
  have h : x ≠ 0
  · exact Ne.symm (ne_of_lt hx)
  exact?
```

The `exact?` tactic is an example of a formal search engine: a tool that, through meta-programming in Lean, compares the current goal with the types of all the available lemmas and returns those with exact matches. Therefore, the key to using `exact?` effectively lies in *gradually developing a certain intuition* about which results are likely to be formalised in Mathlib, and the concrete way in which they are formulated.

Indeed, recognising that a Mathlib lemma about division by $`x` probably required the hypothesis $`x\neq0` (and not simply $`x>0`) was essential to being able to apply `exact?` successfully in the previous example.

Besides `exact?`, there are similar tactics such as `apply?` and `rw?`, which work in the same way and allow intermediate steps to be taken. However, in practice these tactics usually return a long list of options, many of which are not relevant or useful. Therefore, when `exact?` is not enough, it is more effective to turn to other search tools.

### Other tools

Throughout this project I have mainly used two external Mathlib search tools: Moogle{citepOther refMoogle}[] and LeanSearch{citep refGao2024Semantic}[]. Both are semantic search engines, which means that they do not limit themselves to searching for literal matches in the text, but instead try to interpret the mathematical meaning of our query and compare it with the results in Mathlib. To do so, they use large language models (LLMs), which make it possible to establish relationships between statements even if they are formulated in different ways. In particular, they accept queries in the following formats{citep refGao2024Semantic}[]:

* Descriptions in natural language
* Names of known theorems
* Mathematical notation (in LaTeX)
* Lean code

For example, if in the previous case the idea of first proving $`x \neq 0` had not occurred to us, we could have searched Moogle for something like _"division by itself is 1"_. In fact, the second result of this search in Moogle is:

![Screenshot of a Moogle search result for the query "division by itself is 1".](figuras/moogle-example.png)

Which is not the same result that `exact?` suggested, but it looks even simpler. We could go back to our example and write

```anchor xdivx_apply_divself (module := UrysohnsLemma.Docs.Automation)
example (x : ℝ) (hx : x > 0) :
    x / x = 1 := by
  apply div_self
```

After which we would only need to prove that $`x \neq 0`.

In general, I have found that LeanSearch works better than Moogle, especially in terms of the relevance of the results obtained. However, at the beginning of the project I only knew about Moogle, and I discovered LeanSearch later, so I have mostly used Moogle.

An example of a real search I needed for this work in LeanSearch was _"subset of set has at most the dimension of the set"_.

![Screenshot of a LeanSearch search result for the query "subset of set has at most the dimension of the set".](figuras/leansearch-example-cropped.png)

The first result that appears is exactly the one I needed. However, before searching for it I had no idea how to formalise the results I was working on, especially because I was not familiar with the `Cardinal` module. This was a clear example of how these tools give access to parts of Mathlib that would otherwise be hard to locate.

Altogether, tools such as `exact?`, LeanSearch or Moogle have been fundamental in making the formalisation process more efficient, allowing one to rely on Mathlib effectively without needing to know it in depth from the start.

## Noncomputable and the axiom of choice

To finish this section on Lean in practice, it is useful to briefly comment on a question that will appear in some of the later definitions: the use of the *axiom of choice* and the `noncomputable` keyword.

In Lean, the axiom of choice is introduced in the following way:

```anchor choice_axiom (module := UrysohnsLemma.Docs.Automation)
axiom choice {α : Sort u} : Nonempty α → α
```

That is, given a non-empty type, `choice` returns an element of that type, although it does not tell us how to find it. For this reason, its use prevents extracting computable information from the result.

Consequently, when we define functions or constructions that depend on `choice`, Lean forces us to mark them as `noncomputable`. An example is the `choose` function, which, given a proof of an existential type, selects a witness:

```anchor choose_def (module := UrysohnsLemma.Docs.Automation)
noncomputable def choose {α : Sort u} {p : α → Prop}
    (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val
```

We will often use `choose` (`Classical.choose`, since it is found in the `Classical` module) in our results, together with the following lemma

```anchor choose_spec_def (module := UrysohnsLemma.Docs.Automation)
theorem choose_spec {α : Sort u} {p : α → Prop}
    (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property
```

which is a proof that the element chosen through `choose` satisfies the properties we asked of it.

The use of `noncomputable` does not represent a problem for us (nor, in general, for the mathematical community), since in this work we are not interested in the constructions being computable: we work with them from a logical and mathematical point of view, not an algorithmic one.

Moreover, using the axiom of choice has a practical advantage: when we use `choose`, the chosen element will always be the same (even if we do not know which one it is), and it will always have the property `choose_spec`. This makes it possible to work with it consistently within a proof and to refer to it several times as if it were a determined object.

In contrast, another way of obtaining a witness from a proof of existence is to use the `obtain` tactic, which is used in the following way:

```
example : (∃ n : ℕ, n > 3) → ∃ m : ℕ, m > 2 := by
intro h   -- h : ∃ n : ℕ, n > 3
obtain ⟨n, hn⟩ := h    -- n : ℕ, hn : n > 3
...
```

The fundamental difference between using the axiom of choice and using `obtain` is that two witnesses obtained through obtain from the same type (for example of type `∃ n : ℕ, n > 3`) will not necessarily be equal, whereas if they were obtained through `Classical.choose` they will always be equal.
