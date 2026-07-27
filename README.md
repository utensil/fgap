# FGAP

Foundational Group-Algebraic Physics (FGAP) studies algebraic structures
motivated by foundational questions in physics beyond the Standard Model. This
repository contains its Lean library, developed alongside expository notes and
worked calculations.

The starting question is whether group algebras provide a useful organizing
level for structures that physics usually introduces separately. Finite groups
and their real group algebras offer a controlled setting for studying actions,
representations, idempotents, simple components, and explicit maps into familiar
algebras. The aim is to derive and compare such structures, rather than identify
them by matching names or dimensions.

Group algebra is a working hypothesis, not a boundary on the mathematics. The
project will also study its relationships with Clifford and Lie algebras,
twisted group algebras, quaternionic and octonionic structures, operator
algebras, and representation categories where they clarify the problem or show
the limits of an associative approach.

Physics guides the choice of mathematical challenges. A proposed physical
correspondence must specify the representation, algebra map, kernel, real form,
involution, or other structure on which it depends. Algebraic decompositions
alone do not determine particles, interactions, observables, or dynamics.

Clifford algebra was the original route into these questions.
[Rob Wilson's group-theoretic work](https://robwilson1.wordpress.com/) supplies
concrete examples of using finite groups to probe physical structure. FGAP
treats that work as one source of problems and intuition, alongside standard
representation theory and independent work such as
[John Baez's survey of the octonions](https://arxiv.org/abs/math/0105155).
Definitions, calculations, and proofs are checked on their own terms.

The Lean layout follows [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
where its conventions apply.
