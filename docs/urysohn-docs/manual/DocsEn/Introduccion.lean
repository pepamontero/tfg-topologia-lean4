import VersoManual
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.Docs (citetOther citepOther citehereOther)
open Docs (refTrinh2024Solving refGeuvers2009Proof refBuzzard2024Formalising)

set_option pp.rawOnError true
set_option docs.bib.lang "en"

#doc (Manual) "Introduction" =>
%%%
tag := "introduccion"
file := "introduccion"
%%%

In recent years, a question that has been around for decades has come back with renewed strength: can machines do mathematics?

The answer, in general, is still no. But with recent advances in artificial intelligence and formal verification, this barrier is starting to shake. Some systems have already managed to prove, in a fully automated way, results at the level of the mathematical olympiads{citep refTrinh2024Solving}[].

A first challenge when trying to get a computer to do mathematics is closing the gap between the language we understand and the language a machine can process. Even though mathematical language is already quite precise, there is still a considerable distance between a proof written in a paper and one that a computer can validate.

Some of the first attempts to create a language in which mathematics would be understandable to a machine go back to projects such as _Automath_ (1967) and _Mizar_ (1973). Nowadays, tools such as Coq, Isabelle, HOL or Lean make it possible to write and verify mathematics with the assistance of a computer. These tools are known as interactive theorem provers (ITPs){citep refGeuvers2009Proof}[].

In this project I focus on learning and using Lean, one of these tools. I am especially interested in this intersection between mathematics and computation: the process of writing mathematics in such a way that a computer accepts it as valid. To me, formalising proofs in Lean feels like solving a complex and challenging puzzle.

I chose Lean over other proof assistants because I had several resources at hand that made it easier to learn, such as courses taught at my Faculty and a large amount of online documentation, thanks to the Lean community. This community is very active, with thousands of users and an extensive library of formalised mathematical results ready to be reused. I also value that its syntax is closer to ordinary mathematical language than that of other systems.

In particular, I decided to work on results from topology because I find it an especially interesting branch (probably influenced by the fame of mugs and doughnuts) and because it is an area abstract enough to put to the test the capabilities of the formal language — as well as my own — in this puzzle of topological pieces.

# Objectives
%%%
file := "objetivos"
%%%

The main objective is to acquire a solid knowledge of the Lean proof assistant, becoming able to formalise simple results from the Mathematics degree.

Once a certain familiarity with the system has been reached, an additional objective is the formalisation of a relevant result that illustrates the difficulties of the process of proving results in a formal language.

To this end, Urysohn's lemma was chosen: a central result of general topology whose proof requires, among other tools, the use of different kinds of induction. This makes it possible to reach a more advanced command of the Lean system, since it involves features that are not elementary.

Finally, through this process of learning and testing, the aim is to come to understand the advantages and the difficulties involved in bringing mathematics into the environment of a proof assistant.

# Work plan
%%%
file := "plan-de-trabajo"
%%%

The first step was to acquire basic knowledge about Lean. To do so, I enrolled in the Lean course taught by CompuMates at the Faculty of Mathematics during the 2023/24 academic year. This gave me some first basic notions and let me start writing small proofs in Lean 3, mainly focused on propositional logic.

From then on, my interest in Lean grew, and I began to study, in a self-taught way, the more recent Lean 4 version, currently under active development. In particular, I followed in detail the online course _Formalising Mathematics 2024_ taught by Kevin Buzzard{citepOther refBuzzard2024Formalising}[], completing the proposed exercises up to chapter 10, devoted to topological spaces.

That chapter was very brief, and only included two examples of concrete topological spaces and some questions about continuity of functions. The exercises I solved during this initial stage can be found in [this repository](https://github.com/pepamontero/Lean4-Buzzard-Exercises).

Given the scarcity of material about topology, I decided to reinforce this learning by taking as a reference the notes I had taken during the Elementary Topology course of the degree. I began to formalise the main results I had seen in class. Part of this work is presented in section 3 of this document.

While making progress on this task, I reached the topic of separation axioms. Since we had not worked with normal spaces during the course, I turned to other sources to understand this notion. It was then that I wrote for the first time in Lean the statement of Urysohn's lemma and, from that point on, I focused the rest of the work on its formalisation.

Finally, since this result was already proved in the official Mathlib library, I have studied that implementation with the aim of understanding its approach and comparing its fundamental ideas with the ones used in my own formalisation.

# Structure of this document
%%%
file := "estructura-del-trabajo"
%%%

This document is organised in four main parts. First, a detailed introduction to the Lean language is presented, including its mathematical foundations and its use as an assistant for proving mathematics.

Next, some results of general topology are introduced. The goal of that section is not to develop a complete theory, but to illustrate through concrete examples how topological properties are formalised and how spaces are described in Lean.

The third part is the core of this work: the process of formalising Urysohn's lemma and its proof is presented in detail. The path followed is described together with the main difficulties encountered along the way and the strategies used to overcome them. The section ends with a comparison with the ideas used in the Mathlib proof.

All the code developed during the project, including the Lean definitions and proofs, is available in [this public repository](https://github.com/pepamontero/tfg-topologia-lean4). This repository complements the written report and makes it easy to reproduce or consult the formal results obtained.

Finally, the conclusions are presented, focusing on the difficulties and advantages of writing proofs in a formal environment such as Lean.
