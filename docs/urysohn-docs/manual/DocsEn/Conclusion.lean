import VersoManual
import Docs.Papers
import DocsEn.Urysohn

open Verso.Genre Manual
open Verso.Code.External

set_option pp.rawOnError true
-- Keep this in every translated chapter so bibliography text renders in English:
set_option docs.bib.lang "en"

set_option verso.exampleProject "../../.."
set_option verso.exampleModule "UrysohnsLemma.Docs.FutureWork"

#doc (Manual) "Conclusion" =>
%%%
tag := "conclusion"
file := "conclusion"
%%%

Throughout this work, three main objectives have been pursued: learning to use Lean as a proof assistant, formalising an advanced-level mathematical result, Urysohn's lemma, and, as a result of both, acquiring a deep understanding of the formal verification process, its advantages and its difficulties. This section presents the main conclusions I have drawn from this experience.

# Learning Lean
%%%
file := "aprendizaje"
%%%

The process of learning Lean has been very smooth. The availability of resources such as Kevin Buzzard's course (_Formalising Mathematics_), the official documentation and other materials created by the community, such as the _Natural Number Game_{margin}[The _Natural number game_ is an interactive game devoted to learning how to work with natural numbers in Lean's tactic mode. See: [https://adam.math.hhu.de/#/g/leanprover-community/nng4](https://adam.math.hhu.de/#/g/leanprover-community/nng4).], made my first steps enormously easier.

However, as I made progress, I began to detect a second, more subtle level of learning: although my solutions to the exercises proposed by Buzzard were correct from a formal point of view (accepted by Lean), they were considerably longer and more convoluted than the solutions proposed in the course.

This made me see that, besides learning to construct valid proofs, there is an additional learning process focused on how to write efficient and elegant proofs in Lean, which requires a deeper understanding of the tactics and the good practices of the language (such as avoiding the overuse of `simp`).

This same situation repeated itself during the formalisation of the basic topology results of the second section. Many of the proofs that appear in this report were initially much longer, more redundant or more confusing. The work of revision and simplification has been constant; as I learned new ways of simplifying problems, I went back over my steps to improve the previous results.

Even so, there is still room for improvement. Compared with the versions available in Mathlib, my proofs could be reduced even further. Nevertheless, I consider that this simplification effort has a reasonable limit in the context of the objectives of this work, since optimising to the maximum usually comes at the expense of code readability. Some Mathlib proofs are very hard to follow precisely because of their high level of compactness.

During this stage I also understood the importance of reusing the definitions existing in Mathlib. Although at the beginning I defined concepts such as continuity, closure or normal spaces on my own, later on I switched to using the standard definitions of the library, which turned out to be much more practical.

This process also forced me to consolidate my understanding of the mathematical concepts I was working with, since formalising them demands facing their definitions with a level of precision and detail that is not usually required when working on paper. Moreover, I got a fairly clear idea of how certain objects can be formalised by comparing my definitions with those of the library that I used afterwards.

Finally, this transition allowed me to start developing a certain intuition about which results are already formalised in Mathlib and in what way they might be written, in order to locate them through tools such as `exact?`. Also, upon running into the limitations of these tools, I learned to use more powerful tools such as LeanSearch or Moogle.

For all of this, including this part in the work seemed especially relevant to me.

# Formalisation of Urysohn's lemma
%%%
file := "formalizacion-urysohn"
%%%

The formalisation of Urysohn's lemma has been, without a doubt, the most demanding part of the work. Since it is a proof with relatively complex mathematical ideas, trying to adapt them to Lean's paradigm, which is much more structured and restrictive, has been an added difficulty. Many intuitions that are immediate on paper require considerable effort to be translated into the formal language.

An example of this is the proof that the sequence of open sets obtained was monotone (the property {ref "eq-star"}[★]). In all the sources consulted, this property is presented as something that follows trivially from the construction. However, in Lean it was necessary to build this part carefully, and finding the right way to do it took me several months.

Of course, once the formalisation was complete, the result was an extensive piece of code hundreds of lines long. In the same way as in the previous stage, I have been simplifying it, mainly by extracting auxiliary results out of the main file so that they could be reused later. In spite of everything, the Mathlib proof we discussed at the end is still significantly shorter.

Beyond this, this experience has made me see that there is a certain way of thinking that develops over time when working with Lean: it is not simply a matter of translating the paper proof line by line, but of finding a formulation that is more computationally suitable. For example, topology in Mathlib is formalised, in general, using the language of filters. In my case, since I was not familiar with this tool, I opted for an alternative strategy that fitted my knowledge better, but which in the end turned out to be much less efficient.

In any case, this effort has been a great opportunity to improve my command of the language. An especially difficult part has been the use of different kinds of induction throughout the proof. Since many of my initial ideas did not work, I ended up writing and proving different variants of induction in order to understand why certain approaches were not valid and how to adapt them correctly.

Another aspect I found complex was cooperating with Lean's type inference. Although in general Lean automatically resolves many typing details, saving a lot of work, sometimes this automation becomes an obstacle. A clear example of this has been having to define a modified version of the function $`F` so that it returned sets in $`\mathbb{R}` instead of in $`\mathbb{Q}` and thus be able to define its real infimum.

However, this difficulty has also led me to learn to use especially useful tools such as the `exact_mod_cast` tactic or the `Subtype.val` function of Mathlib.

In summary, this process has been key to consolidating my knowledge of Lean and understanding how to approach the formalisation of complex mathematical results within an assisted environment.

# Possible improvements and extensions
%%%
file := "mejoras"
%%%

There are several directions in which the work done could be extended or improved:

* *Systematic use of Mathlib definitions*

  Although in early versions I used my own definitions for certain concepts, later on I replaced them with the Mathlib definitions. However, there are still some objects that I have not managed to integrate completely, such as the definition of topological subspace or that of the usual topology.

  The goal of this work was not primarily to make the result reusable in other developments, since the formalisation of Urysohn's lemma already exists in Mathlib, but to understand the formalisation process in detail and reflect on the difficulties that may arise. Nevertheless, it would be interesting to rewrite the proof in such a way that only standard Mathlib definitions and constructions are used, in order to go deeper into their implementations and usage patterns.

  In particular, it is proposed to express the theorem in the following form:

  ```anchor urysohn_mathlib_statement
  theorem Urysohn {X : Type} [T : TopologicalSpace X]
      [N : NormalSpace X] {s t : Set X} (hs : IsClosed s)
      (ht : IsClosed t) (hd : Disjoint s t) :
      ∃ f : X → ℝ, Continuous f ∧ Set.EqOn f 0 s ∧ Set.EqOn f 1 t
        ∧ ∀ x, f x ∈ Set.Icc 0 1 := by
    sorry
  ```

  In this statement, the topology accompanying the space of real numbers is automatically assumed in the definition of continuity through an instance that Lean infers by default. Therefore, it would only remain to check that this instance corresponds to the definition of the usual topology I have used, by proving this result:

  ```anchor my_usual_equiv_statement
  lemma my_usual_equiv : @UniformSpace.toTopologicalSpace ℝ
      (by exact PseudoEMetricSpace.toUniformSpace) = UsualTopology := by
    sorry
  ```

* *Code documentation*

  A possible improvement would be to write the documentation of the code following the style used in Mathlib's. The Lean community offers a tool that generates this kind of documentation automatically from the comments written in the `.lean` files{margin}[See: `https://github.com/leanprover-community/doc-gen`.]. Another option could be to use a tool such as _leanblueprint_, which makes it possible to create and publish, in an automated way, a presentation of the project in the form of a "blueprint"{margin}[See: `https://github.com/PatrickMassot/leanblueprint`.].

* *Topology Game*

  An interesting line would be to design a resource similar to the _Natural Number Game_, but focused on introducing the basic concepts of topology formalised in Lean. This would not only reinforce my own learning, but could also be useful for other people interested in getting started with Lean in the context of topology. In fact, a game with this idea already exists{margin}[See: [https://mmasdeu.github.io/topologygame/](https://mmasdeu.github.io/topologygame/)], but it uses the Lean 3 version, so it would be interesting to update it.

  Moreover, this kind of game is developed directly in Lean using an already available base{margin}[See: `https://github.com/leanprover-community/lean4game/blob/main/doc/create_game.md`.], which also offers the opportunity to explore Lean as a functional programming language, beyond its use as a proof verifier.

* *Lean as a program verifier*

  Finally, it is worth mentioning that I have been admitted to the Master's in Formal Methods in Computer Science (UCM with UPM). This will allow me to continue exploring Lean and other verifiers from a new perspective: the use of these tools in the verification of programs and formal specifications. I believe this training will naturally complement the work done in this project, since it will allow me to go deeper into another relevant and current facet of verification systems.
