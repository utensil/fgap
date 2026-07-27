# FGAP

FGAP is read "F-gap," for the foundational gap between established mathematical
tools and open questions about physical structure, especially beyond the
Standard Model. It is also a coined acronym for Foundational Group-Algebraic
Physics.

This repository studies mathematical structures that may help us understand
physical structure more deeply. It does not construct or claim a physical
theory. Its Lean library is developed alongside expository notes and worked
calculations.

The starting question is whether group algebras provide a useful organizing
level for structures that physics usually introduces separately. Finite groups
and their real group algebras offer a controlled setting for studying actions,
representations, idempotents, simple components, and explicit maps into familiar
algebras. The aim is to make these relationships explicit through
constructions, representations, and proofs.

Group algebra is the current working hypothesis. The mathematical scope remains
broader: the project will also study its relationships with Clifford and Lie
algebras, twisted group algebras, quaternionic and octonionic structures,
operator algebras, and representation categories where they clarify the
question or show the limits of an associative approach.

Each candidate is examined on its own mathematical terms: its definitions,
representations, invariants, decompositions, and relationships with other
structures. When a physics-motivated correspondence is discussed, the
representation, algebra map, kernel, real form, involution, or other required
data must be stated explicitly.

Clifford algebra was the original route into these questions.
[Rob Wilson's group-theoretic work](https://robwilson1.wordpress.com/) supplies
concrete examples of using finite groups to probe physical structure. FGAP takes
inspiration from that work alongside representation theory and exploratory work
in other directions, including octonions. Definitions, calculations, and proofs
are checked on their own terms.

The Lean code and project workflow follow applicable conventions from
[Tau Ceti](https://github.com/TauCetiProject/TauCeti).
