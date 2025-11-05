# Preface
It was my great honor to work under the guidance of my advisor, Professor Pedro Morales-Almazan, and a new “crazy" idea began to take shape, one that bridges classical analysis with modern proof technology.  This thesis project is still early work. Our goal is not to rush toward completion but to understand deeply what it means to "proof" mathematics. We discussed a lot of ideas and found that a shared interest topic was Weyl’s Theorem.

The thesis will bring the idea of the Laplace eigenvalue problem gives us a sequence of eigenvalues, and that Weyl’s law describes the asymptotic growth rate of these eigenvalues, depending on the dimension of the domain where the equation is defined. Therefore, we also check the Laplace equation in bounded domains, for example, a segment, a rectangle, a disk, etc. While we studied those topics in a physical book and notes, formalizing this result within a proof assistant like Lean—guided and supported by modern large language models—offered an entirely new mode of engagement. To be honest, it's taken a long time for us and it's not easy to "translate" between the mathematical proof language and LEAN.

# FILE in this project
The LEAN 4 project contains my exploratory work on formalizing parts of the Weyl Law using the Lean 4 theorem prover.

1. File Main.lean and test_1.lean are inspired by examples found online and serves as both a learning exercise
2. File Wey Law lean 4 is the prototype (Chapter 5), where I discuss the the proof and lean 4 about the Weyl asymptotic formula.

# A big thanks to LEAN Community.
References Github User: 
1. https://github.com/leanprover-community

2. https://github.com/leanprover-community/mathlib4?tab=readme-ov-file

3. https://github.com/PatrickMassot/verbose-lean4/tree/master
