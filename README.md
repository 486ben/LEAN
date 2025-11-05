# Preface
It was my great honor to work under the guidance of my advisor, Professor Pedro Morales-Almazan, and a new “crazy" idea began to take shape, one that bridges classical analysis with modern proof technology.  This thesis project is still early work. Our goal is not to rush toward completion but to understand deeply what it means to "proof" mathematics. We discussed a lot of ideas and found that a shared interest topic was Weyl’s Theorem.

The thesis will bring the idea of the Laplace eigenvalue problem gives us a sequence of eigenvalues, and that Weyl’s law describes the asymptotic growth rate of these eigenvalues, depending on the dimension of the domain where the equation is defined. Therefore, we also check the Laplace equation in bounded domains, for example, a segment, a rectangle, a disk, etc. While we studied those topics in a physical book and notes, formalizing this result within a proof assistant like Lean—guided and supported by modern large language models—offered an entirely new mode of engagement. To be honest, it's taken a long time for us and it's not easy to "translate" between the mathematical proof language and LEAN.

# FILE in this project
The LEAN 4 project contains my exploratory work on formalizing parts of the Weyl Law using the Lean 4 theorem prover.

1. File Main.lean and test_1.lean are inspired by examples found online and serves as both a learning exercise
2. File Wey Law lean 4 is the prototype (Chapter 5), where I discuss the the proof and lean 4 about the Weyl asymptotic formula.
3. Python File with 1D,2D,3D will better show the ideas of Laplacian operator and wey law: https://colab.research.google.com/drive/1ZmCqLNCnyB3Km47dtLFjR-bNuIEGL67C?usp=sharing

# Picture Python Code
To complement the formalization work in Lean 4, Professor Pedro and I also wrote a short Python script to visualize the relationship between Weyl’s Law and the Laplacian operator. The code computes the eigenvalues of the Laplacian on a simple rectangular domain (for example, a unit square with Dirichlet boundary conditions) and compares the actual eigenvalue counting function with the asymptotic prediction given by Weyl’s Law. By plotting both curves on the same graph, it highlights how the discrete Laplacian spectrum gradually approaches the continuous Weyl asymptotic behavior as the eigenvalue index increases. This serves as an intuitive numerical illustration of the theorem discussed in Chapter 3 of my thesis. below are the picture in different dimension.
<img width="989" height="590" alt="image" src="https://github.com/user-attachments/assets/ea0c1857-8439-47b6-b21b-e2c3198cb6a4" />
<img width="990" height="590" alt="image" src="https://github.com/user-attachments/assets/16b56987-8b60-4147-a68d-dfcb8a1a17cc" />
<img width="1016" height="702" alt="image" src="https://github.com/user-attachments/assets/26c6f59e-f6e0-4ded-8bca-ced16cb8be3f" />
<img width="989" height="590" alt="image" src="https://github.com/user-attachments/assets/e9b976d5-ce23-4a3b-a9f0-b5272b796a19" />
<img width="989" height="590" alt="image" src="https://github.com/user-attachments/assets/d541224d-4ec1-45e9-ae0e-728f43e3514b" />



# Wey Law lean 4 prototype's idea.
Inside the Weyl Law Lean 4, I begins by importing several core components from Mathlib, including foundational results in real analysis, topology, metric spaces, measure theory, and trigonometric functions. These imports provide the necessary math framework to formalize concepts such as bounded domains, open sets, and eigenvalues of the Laplacian.

Inside the file, the code outlines a structured three step template inspired by the proof strategy described in Chapter 5.1 of my thesis. Although the proofs are not yet complete, this framework serves as a reference for future formalization work:

Step 1: We need to first show the Rectangular Domains – Defines rectangles in ℝ², shows they form bounded open sets, and states Weyl’s Law for rectangular regions.

Step 2: We need to show the Finite Unions of Rectangles – Extends the theory to finite unions of disjoint rectangles, establishing their area, boundedness, and a formal statement of Weyl’s Law for these composite domains.

Step 3: We need to show the Approximation and General Domains – Introduces inner and outer approximations of arbitrary bounded domains by rectangles, setting up the framework for proving Weyl’s Law in the general case via approximation arguments and eigenvalue monotonicity.

Although many parts are marked with sorry (placeholders for unfinished proofs), the code provides a conceptual and syntactic foundation for formalizing the Weyl asymptotic formula within Lean 4. Because many results are still missing from Mathlib, this file functions could be an roadmap for later researchers who wish to continue the formalization.

# A big thanks to LEAN Community.
References Github User: 
1. https://github.com/leanprover-community

2. https://github.com/leanprover-community/mathlib4?tab=readme-ov-file

3. https://github.com/PatrickMassot/verbose-lean4/tree/master
